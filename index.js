
// largely based on: https://github.com/seiya-dev/hidive-downloader-nx/blob/master/hidive.js

const pUrl = require('url')

const { config, proxy, persist } = require('internal')

const needle = require('needle')
const cheerio = require('cheerio')
const async = require('async')
const crypto = require('crypto-js')
const m3u = require('m3u8-reader')

const shlp = {
	cookie: {
		make: (data, keys) => {
		    let res = [];
		    for (let key of keys) {
		        if (typeof data[key] !== 'object') continue;
		        res.push(`${key}=${data[key].value}`);
		    }
		    return res.join('; ');
		},
		parse: data => {
		    let res = {};
		    for (let line of data) {
		        let c = line.split('; ');
		        let val = c.shift().split('=');
		        res[val[0]] = {
		            value: val.slice(1).join('=')
		        };
		        for (let f of c) {
		            let param = f.split('=');
		            if (param[0].toLowerCase() === 'expires') {
		                res[val[0]].expires = new Date(param[1]);
		            } else if (param[1] === undefined) {
		                res[val[0]][param[0]] = true;
		            } else {
		                res[val[0]][param[0]] = param[1];
		            }
		        }
		    }
		    return res;
		}
	}
}

const defaults = {
	name: 'HIDIVE',
	prefix: 'hidive_',
	origin: '',
	endpoint: 'https://www.hidive.com',
	icon: 'https://cdn.myanimelist.net/s/common/uploaded_files/1497990382-d769797f8b53cf7e0a828d46c1e5b4aa.jpeg',
	categories: []
}

const api = {
    "apihost"  : "https://api.hidive.com",
    "apikey"   : "6e6b1afcf0800e2ba312bce28d1dbccc87120904",
    "devName"  : "Android",
    "appId"    : "24i-Android",
    "clientWeb": "okhttp/3.4.1",
    "clientExo": "smartexoplayer/1.6.0.R (Linux;Android 6.0) ExoPlayerLib/2.6.0"
}

let endpoint = defaults.endpoint

const episodes = {}

const videoUrls = {}

const headers = {
	'accept': 'application/json, text/plain, */*',
	'accept-language': 'en-GB,en-US;q=0.9,en;q=0.8',
	'referer': endpoint,
	'user-agent': 'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_13_6) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/73.0.3683.103 Safari/537.36',
}

function setEndpoint(str) {
	if (str) {
		let host = str
		if (host.endsWith('/index.php'))
			host = host.replace('/index.php', '/')
		if (!host.endsWith('/'))
			host += '/'
		endpoint = host
		const origin = endpoint.replace(pUrl.parse(endpoint).path, '')
		headers['origin'] = origin
		headers['referer'] = endpoint + '/'
	}
	return true
}

setEndpoint(defaults.endpoint)

function retrieveManifest() {
	function manifest() {
		return {
			id: 'org.' + defaults.name.toLowerCase().replace(/[^a-z]+/g,''),
			version: '1.0.0',
			name: defaults.name,
			description: 'Anime from HIDIVE - Subcription needed',
			resources: ['stream', 'meta', 'catalog', 'subtitles'],
			types: ['series', 'anime'],
			idPrefixes: [defaults.prefix],
			icon: defaults.icon,
			catalogs: [
				{
					id: defaults.prefix + 'catalog',
					type: 'anime',
					name: defaults.name,
					genres: ['simulcasts', 'dubs', 'series', 'movies'],
					extra: [{ name: 'genres' }, { name: 'skip' }, { name: 'search' }]
				}
			]
		}
	}

	return new Promise((resolve, reject) => {
		resolve(manifest())
	})
}

function toMeta(args, obj) {
	let releasedTime = Date.now()
	let isOva = false
	let isMovie = false
	if (obj.ShowInfoTitle.match(/OVA/i)) {
		isOva = true
	} else if (obj.ShowInfoTitle.match(/Theatrical/i)) {
		isMovie = true
	}
	let i = 0
	return {
		id: defaults.prefix + (isOva ? 'ova_' : isMovie ? 'movie_' : '') + obj.Id,
		name: obj.Name,
		type: 'series',
		description: obj.ShortSynopsis,
		poster: 'https:' + obj.MasterArtUrl,
		posterShape: 'landscape',
		background: 'https:' + obj.KeyArtUrl,
		imdbRating: obj.OverallRating ? ((obj.OverallRating * 2) + '') : null,
		runtime: obj.RunTime ? obj.RunTime + 'min' : null,
		releaseInfo: obj.FirstPremiereDate ? obj.FirstPremiereDate.split('-')[0] : null,
		logo: 'https:' + obj.RokuSDArtUrl,
		videos: (obj.Episodes || []).map(ep => {
			if (isOva) {
				if (ep.DisplayNameLong.match(/OVA/i)) {
					i++
					releasedTime -= 86400000
					episodes[args.id + ':1:' + i] = ep.VideoKey
					return {
						name: 'OVA #' + i,
						season: '1',
						number: i,
						released: new Date(releasedTime).toISOString()
					}
				} else {
					return {}
				}
			} else if (isMovie) {
				if (ep.DisplayNameLong.match(/Theatrical/i)) {
					i++
					releasedTime -= 86400000
					episodes[args.id + ':1:' + i] = ep.VideoKey
					return {
						name: 'Movie #' + i,
						season: '1',
						number: i,
						released: new Date(releasedTime).toISOString()
					}
				} else {
					return {}
				}
			} else {
				episodes[args.id + ':1:' + ep.EpisodeNumberValue] = ep.VideoKey
				releasedTime -= 86400000
				return {
					name: ep.Name,
					season: '1',
					number: ep.EpisodeNumberValue,
					released: new Date(releasedTime).toISOString()
				}
			}
		})
	}
}

const subtitles = []

const dbs = {}

// Generate Nonce
function generateNonce(){
    const initDate = new Date()
    const nonceDate = [
        initDate.getUTCFullYear().toString().slice(-2), // yy
        ('0'+(initDate.getUTCMonth()+1)).slice(-2),     // mm
        ('0'+initDate.getUTCDate()).slice(-2),          // dd
        ('0'+initDate.getUTCHours()).slice(-2),         // HH
        ('0'+initDate.getUTCMinutes()).slice(-2)        // MM
    ].join(''); // => "yymmddHHMM" (UTC)
    const nonceCleanStr = nonceDate + api.apikey
    const nonceHash = crypto.SHA256(nonceCleanStr).toString(crypto.enc.Hex)
    return nonceHash
}

// Generate Signature
function generateSignature(body){
    const sigCleanStr = [
        client.ipAddress,
        api.appId,
        client.deviceId,
        client.visitId,
        client.profile.userId,
        client.profile.profileId,
        body,
        client.xNonce,
        api.apikey,
    ].join('');
    return crypto.SHA256(sigCleanStr).toString(crypto.enc.Hex)
}

// getData
async function getData(reqUrl){
    return await reqData(reqUrl, '', 'GET');
}

// cookies
let session = {}

// load cookies
if (persist.getItem('session')) {
    session = persist.getItem('session')
    let hasError = false
    for (let key in session) {
    	if ((session[key] || {}).expires) {
    		// if any cookie expires less then 1 day from now, refresh them
    		if (session[key].expires < Date.now() + 86400000) {
    			hasError = true
    		}
    	}
    }
    if (hasError) {
		session = {}
		persist.removeItem('session')
	}
}

// client default
let client = {
    // base
    ipAddress : '',
    xNonce    : '',
    xSignature: '',
    // personal
    deviceId: '',
    visitId : '',
    // profile data
    profile: {
        userId   : 0,
        profileId: 0,
    },
}

if (persist.getItem('profile'))
	client.profile = persist.getItem('profile')

// postApi
async function reqData(method, body, type){
    let options = { headers: {} };
    // get request type
    const isGet = type == 'GET' ? true : false;
    // set request url and user agent
    const url     = ( !isGet ? api.apihost + '/api/v1/' : '') + method;
    options.headers['user-agent'] = isGet ? api.clientExo : api.clientWeb;
    // set api data
    if(!isGet){
        body      = body == '' ? body : JSON.stringify(body);
        client.xNonce     = generateNonce();
        client.xSignature = generateSignature(options.body);
        // set api headers
        options.headers = Object.assign({
            'Content-Type'   : 'application/x-www-form-urlencoded; charset=UTF-8',
            'X-ApplicationId': api.appId,
            'X-DeviceId'     : client.deviceId,
            'X-VisitId'      : client.visitId,
            'X-UserId'       : client.profile.userId,
            'X-ProfileId'    : client.profile.profileId,
            'X-Nonce'        : client.xNonce,
            'X-Signature'    : client.xSignature,
        }, options.headers);
        // cookies
        let cookiesList = Object.keys(session);
        if(cookiesList.length > 0) {
            options.headers.Cookie = shlp.cookie.make(session, cookiesList);
        }
    }
    // check m3u8 request and ssp param
    try {
    	let res
    	if (isGet) {
    		res = await needle('get', url, options)
    		if (!res) {
    			console.error(defaults.name + ' - Failed request to api')
    		}
    	} else {
    		res = await needle('post', url, body, options)
    	}
        if(!isGet && res.headers && res.headers['set-cookie']) {
            const newReqCookies = shlp.cookie.parse(res.headers['set-cookie'])
            delete newReqCookies.AWSALB
            delete newReqCookies['.AspNet.ExternalCookie']
            delete newReqCookies.Campaign
            session = Object.assign(newReqCookies, session)
            if (session.Visitor || session.VisitId || session['.AspNet.ApplicationCookie']) {
                persist.setItem('session', session)
            }
        }
        if(!isGet) {
            const resJ = res.body
            if(resJ.Code > 0) {
                console.log(`${defaults.name} - [ERROR] Code ${resJ.Code} (${resJ.Status}): ${resJ.Message}\n`)
                return {
                    ok: false,
                    res,
                }
            }
        }
        return {
            ok: true,
            res,
        }
    }
    catch(error){
        if(error.statusCode && error.statusMessage) {
            console.log(`\n${defaults.name} - [ERROR] ${error.name} ${error.statusCode}: ${error.statusMessage}\n`)
        } else {
        	console.log(error)
            console.log(`\n${defaults.name} - [ERROR] ${error.name}: ${error.code}\n`)
        }
        return {
            ok: false,
            error,
        }
    }
}

// init
async function doInit(){
    const newIp = await reqData('Ping', '');
    if(!newIp.ok){return false;}
    client.ipAddress = newIp.res.body.IPAddress;
    const newDevice = await reqData('InitDevice', {"DeviceName":api.devName});
    if(!newDevice.ok){return false;}
    client.deviceId = newDevice.res.body.Data.DeviceId;
    client.visitId  = newDevice.res.body.Data.VisitId;
    return true;
}

// Auth
async function doAuth(){
    const aInit = await doInit();
    if(!aInit){return;}
    console.log(`${defaults.name} - [INFO] Authentication`);
    if (Object.keys(session).length) {
	    console.log(`${defaults.name} - [INFO] Using Previous Auth Session`);
    	return true
    } else {
	    const auth = await reqData('Authenticate', {"Email":config.email,"Password":config.password});
	    if(!auth.ok){return;}
	    const authData = auth.res.body.Data;
	    client.profile.userId    = authData.User.Id;
	    client.profile.profileId = authData.Profiles[0].Id;
	    persist.setItem('profile', client.profile)
	    console.log(`${defaults.name} - [INFO] Auth complete!`);
	    console.log(`${defaults.name} - [INFO] Service level for "${config.email}" is ${authData.User.ServiceLevel}`);
	}
}

async function retrieveRouter() {

	await doAuth()

	const manifest = await retrieveManifest()

	const { addonBuilder, getInterface, getRouter } = require('stremio-addon-sdk')

	const builder = new addonBuilder(manifest)

	builder.defineCatalogHandler(args => {
		return new Promise(async (resolve, reject) => {
			const extra = args.extra || {}
			if (extra.search) {
			    const searchItems = await reqData('Search', { "Query": extra.search })
			    if(!searchItems.ok) {
			    	reject(defaults.name + ' - Could not get search results')
			    } else if ((((((searchItems || {}).res || {}).body || {}).Data || {}).TitleResults || []).length) {
			    	resolve({ metas: searchItems.res.body.Data.TitleResults.map(el => { return toMeta(args, el) }) })
			    }
			} else {
				if (!extra.genre)
					reject(defaults.name + ' - Unsupported catalog request')
				else {
					const genre = extra.genre == 'series' ? 'tv' : extra.genre
					if (!dbs[genre]) {
						needle.get(defaults.endpoint + '/' + genre, { headers }, (err, resp, body) => {
							if (!err && body) {
								const $ = cheerio.load(body)
								const results = []
								const type = $('.information .display-table .text-container h2').text().trim()
								let isMovie
								let isOva
								if (type) {
									if (type == 'Feature')
										isMovie = true
									else if (type == 'OVA')
										isOva = true
								}
								$('.cell').each((ij, el) => {
									let isOva = false
									let isMovie = false
									let href = $(el).find('a').attr('href')
									if (href.includes('-ova/'))
										isOva = true
									else if (extra.genre == 'ova')
										isOva = true
									else if (extra.genre == 'movies')
										isMovie = true
									let poster = $(el).find('.default-img img').attr('data-src')
									if (!poster)
									    poster = $(el).find('.default-img img').attr('src')
									if (poster && poster.startsWith('//'))
										poster = 'https:' + poster
									results.push({
										id: defaults.prefix + (isOva ? 'ova_' : isMovie ? 'movie_' : '') + $(el).attr('data-id'),
										name: $(el).find('.player a').attr('data-title'),
										poster,
										posterShape: 'landscape',
										type: 'series'
									})
								})
								if (results.length) {
									dbs[genre] = results
									const skip = parseInt(extra.skip || 0)
									resolve({ metas: results.slice(skip, skip + 70) })
								} else
									reject(defaults.name + ' - Unexpected catalog response')
							} else
								reject(defaults.name + ' - Invalid catalog response')
						})
					} else {
						const skip = parseInt(extra.skip || 0)
						resolve({ metas: dbs[genre].slice(skip, skip + 70) })
					}
				}
			}
		})
	})

	builder.defineMetaHandler(args => {
		return new Promise(async (resolve, reject) => {
			let id = args.id.replace(defaults.prefix, '')
			let type
			if (id.includes('_'))
				id = id.split('_')[1]
			const getShowData = await reqData('GetTitle', { "Id": id })
			const showData = ((((getShowData || {}).res || {}).body || {}).Data || {}).Title
			if (!showData)
				reject(defaults.name + ' - Could not get metadata for id: ' + id)
			else
				resolve({ meta: toMeta(args, showData) })
		})
	})

	builder.defineStreamHandler(args => {
		return new Promise(async (resolve, reject) => {
			let videoKey = episodes[args.id]
			if (!videoKey)
				videoKey = episodes[args.id.replace('_movie', '').replace('_ova', '')]
			if (videoKey) {
				let id = args.id.replace(defaults.prefix, '').split(':')[0]
				if (id.includes('_'))
					id = id.split('_')[1]
				let getVideoData = await reqData('GetVideos', {
					"VideoKey": videoKey,
					"TitleId": id
				})
	            if(getVideoData.ok){
	                let videoData = getVideoData.res.body.Data
	                if (!subtitles[args.id])
					    subtitles[args.id] = []
	                for (let key in ((videoData || {}).CaptionVttUrls || {})) {
	                	subtitles[args.id].push({
	                		url: videoData.CaptionVttUrls[key],
	                		lang: key || 'English'
	                	})
	                }
	                const streamUrls = []
	                for (let name in ((videoData || {}).VideoUrls || {})) {
	                	const stream = videoData.VideoUrls[name]
	                	for (let format in stream) {
	                		const i = 0
	                		stream[format].forEach(url => {
	                			streamUrls.push({ title: name.split(', ').join(' | ') + ', ' + format.toUpperCase(), url })
	                		})
	                	}
	                }
	                if (streamUrls.length) {
	                	const streams = []
	                	const q = async.queue((task, cb) => {
	                		const doTask = async () => {
		                		const m3uData = await needle('get', task.url)
		                		if (m3uData) {
		                			const data = m3u(m3uData.body)
		                			let inf
		                			(data || []).forEach(el => {
		                				if (typeof el === 'object' && (el || {})['STREAM-INF']) {
		                					if (el['STREAM-INF'].RESOLUTION) {
		                						inf = el['STREAM-INF'].RESOLUTION.split('x')[1]
		                					}
		                				} else if (typeof el == 'string') {
		                					streams.push({
		                						title: task.title + ' | ' + inf + 'p',
		                						url: el
		                					})
		                				}
		                			})
		                		} else {
		                			streams.push(task)
		                		}
		                		cb()
		                	}
		                	doTask()
	                	})
	                	q.drain = () => {
	                		if (streams.length)
	                			resolve({ streams })
	                		else
	                			reject(defaults.name + ' - Could not parse any streams: ' + args.id.replace(defaults.prefix, ''))
	                	}
	                	streamUrls.forEach(el => {
	                		q.push(el)
	                	})
	                } else
	                	reject(defaults.name + ' - No streams found for: ' + args.id.replace(defaults.prefix, ''))
	            } else 
	            	reject(defaults.name + ' - Unexpected response from video api: ' + args.id.replace(defaults.prefix, ''))
	        } else {
	        	reject(defaults.name + ' - Unable to get details on episode for id: ' + args.id.replace(defaults.prefix, ''))
	        }
	    })
	})

	builder.defineSubtitlesHandler(args => {
		return new Promise((resolve, reject) => {
			resolve({ subtitles: subtitles[args.id] || [] })
		})
	})

	const addonInterface = getInterface(builder)

	return getRouter(addonInterface)

}

module.exports = retrieveRouter()
